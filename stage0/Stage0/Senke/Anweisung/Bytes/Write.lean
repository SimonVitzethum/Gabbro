/- Subject: Reusing the ordinary expression and store proofs for captured byte spans. -/
import Stage0.Senke.Anweisung.Bytes.Code
import Grammatik.Nichtinterferenz.LokalSchritt
import Stage0.Senke.Anweisung.Schreiben
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration}

theorem enc_int_cast_back {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D (.int a b)) (w : Runner.W) :
    Enc τ (cast (congrArg (Wert D) h).symm v) w ↔ w = BitVec.ofInt 64 v.n := by
  cases h; rfl

theorem dropBytes_nonneg {z : Int} (hz : 0 ≤ z) : (j : Nat) → 0 ≤ dropBytes j z
  | 0 => hz
  | j + 1 => Int.ediv_nonneg (dropBytes_nonneg hz j) (by decide)

theorem byteQuot_eval {Γ : Ctx} {Λ : List (Res D)} {a b H : Int}
    (z : Zahl 0 H) (k : Zahl a b) (ρ : Env D Γ) (σ₀ σ : World D) :
    (j : Nat) → (eval σ₀ (byteQuot (Λ := Λ) a b H j) σ (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ))).n = dropBytes j z.n
  | 0 => rfl
  | j + 1 => by
    simp only [byteQuot, eval, Zahl.div, dropBytes]
    rw [byteQuot_eval z k ρ σ₀ σ j, Int.tdiv_eq_ediv_of_nonneg (dropBytes_nonneg z.lo_le j)]

theorem putBytesL_top {L : Lay D} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {f : D.Feld t}
    {a b H : Int} {hlo : 0 ≤ a} {n j : Nat} {hhi : b + j + n ≤ D.count t} {c : List II} {top : Nat}
    (h : putBytesL L (Γ := Γ) (Λ := Λ) t f a b H hlo n j hhi = some (c, top)) : frei Γ + 2 ≤ top := by
  cases n with
  | zero => simp only [putBytesL, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n =>
    simp only [putBytesL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨ce, _, ci', _, ca, ha, rest, _, h⟩ := h
    have := slotA_top ha
    simp only [Prod.mk.injEq] at h
    omega

/-- The captured index and value stay in their original slots while every byte is written.
    The synthetic expressions only read that environment, even when a prior byte changed the world. -/
theorem putBytesL_ok {L : Lay D} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {f : D.Feld t}
    (hf : D.typ t f = .int 0 255) {a b H : Int} (hlo : 0 ≤ a)
    {fp : Runner.W} {Ks K : Nat} (hW : WIn L fp Ks K)
    (z : Zahl 0 H) (k : Zahl a b) (ρ : Env D Γ) :
    (n j : Nat) → (hhi : b + j + n ≤ D.count t) → (c : List II) → (top : Nat) →
    putBytesL L (Γ := Γ) (Λ := Λ) t f a b H hlo n j hhi = some (c, top) → top ≤ Ks →
    ∀ m pc σ, PreS m pc fp K (frei Γ + 2) c (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) → WeltAt m L σ →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      AgreeW L fp (frei Γ + 2) K m m' ∧ EnvAt m' fp (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) ∧
      WeltAt m' L (σ.schreibBytes t f hf Λ (k.n + j) (zahlZuBytes n (dropBytes j z.n)))
  | 0, j, hhi, c, top, h, _, m, pc, σ, hp, hw => by
    simp only [putBytesL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, by simpa using Star.refl _ m, AgreeW.refl _ _ _ _ _, hp.env, hw⟩
  | n + 1, j, hhi, c, top, h, hK, m, pc, σ, hp, hWa => by
    simp only [putBytesL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨ci', ti⟩, hi, ⟨ca, ta⟩, ha, ⟨rest, tr⟩, hr, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    let ix := byteIndex (Γ := Γ) (Λ := Λ) t a b H j hlo (by omega)
    let part := eval σ (bytePart (Γ := Γ) (Λ := Λ) a b H j) σ (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ))
    have hpn : part.n = dropBytes j z.n % 256 := by
      simp only [part, bytePart, eval, Zahl.rem]
      rw [byteQuot_eval, Int.tmod_eq_emod_of_nonneg (dropBytes_nonneg z.lo_le j)]
    have hp' : PreS m pc fp K (frei Γ + 2) ((ce ++ ca ++ [stC (frei Γ + 2)]) ++ rest) (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) := hp
    have hixn : (eval σ ix σ (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ))).n = k.n + j := rfl
    have hk0 : 0 ≤ k.n + j := by have := k.lo_le; omega
    have hkc : (((k.n + j).toNat : Nat) : Int) < D.count t := by
      have := k.le_hi; have := Int.toNat_of_nonneg hk0; omega
    have hkn : (((k.n + j).toNat : Nat) : Int) = k.n + j := Int.toNat_of_nonneg hk0
    have htop := slotA_top ha
    obtain ⟨m1, s1, a1, en1, hw1⟩ := store_ok hp'.left hW hWa (by omega)
      (fun m pc hp => (lowE_ok σ σ (fun _ h => h) (bytePart a b H j) _ ce te he (by omega) m pc _ hp).mono
        (fun w hw => (enc_int_cast_back hf part w).mpr hw))
      (fun m pc hp => slotA_ok (σ₀ := σ) (σ := σ) (i := ix) ha (by omega)
        (fun m pc hp => lowE_ok σ σ (fun _ h => h) ix _ ci' ti hi (by omega) m pc _ hp) hp)
      (by simpa only [hixn] using (hW.lay.1 t f (k.n + j).toNat hkc))
      (fun m w hm hw => by
        have hnw : Enc (D.typ t f) (cast (congrArg (Wert D) hf).symm part) w := hw
        have hh := weltAt_slot hm hW.lay hW.dis hkc hnw
        rw [hkn] at hh
        exact hh)
    have hcf := codeFar_right (n := (ce ++ ca ++ [stC (frei Γ + 2)]).length) (k := rest.length) (by simpa only [List.length_append] using hp'.far)
    have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * (ce ++ ca ++ [stC (frei Γ + 2)]).length)) fp K
        (frei Γ + 2) rest (Env.cons (τ := .int a b) k (Env.cons (τ := .int 0 H) z ρ)) :=
      ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1,
        codeAt_agreeWIn hW a1 (codeAt_right hp'.code) hcf, hcf, en1, trivial, wstab_true _ _⟩
    have hw1' : WeltAt m1 L ((σ.schreibSlot t Λ (k.n + j) f (cast (congrArg (Wert D) hf).symm part))) := hw1
    obtain ⟨m2, s2, a2, en2, hw2⟩ := putBytesL_ok hf hlo hW z k ρ n (j + 1) _ rest tr hr (by omega) m1 _ _ hp1 hw1'
    refine ⟨m2, s1.trans ?_, a1.trans a2, en2, ?_⟩
    · simpa only [List.length_append, List.length_singleton, pc_add] using s2
    · have hb : part = (⟨dropBytes j z.n % 256, Int.emod_nonneg _ (by decide), by
          have := Int.emod_lt_of_pos (dropBytes j z.n) (show (0 : Int) < 256 by decide); omega⟩ : Byte) := by
        apply Gabbro.Grammatik.zahl_ext; exact hpn
      simpa only [zahlZuBytes, World.schreibBytes, dropBytes, hb, Int.natCast_add, Int.natCast_one, Int.add_assoc] using hw2

end Gabbro.Stage0.Senke
