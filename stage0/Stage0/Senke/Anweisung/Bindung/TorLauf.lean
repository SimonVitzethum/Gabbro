/-
  File:      stage0/Stage0/Senke/Anweisung/TorLauf.lean
  Subject:   **The call of a gate** (`torC_ok`): the code of `torC` builds the request -- the arguments' words in the
             first argument registers, zero in the others, the number -- and the kernel answers it (`TorOK`): the
             memory then holds the oracle's world, slot `s` the kernel's word, which is the oracle's raw answer; no slot
             below `s` changed.
-/
module
public import Stage0.Senke.Anweisung.Bindung.TorLaufa
public import Stage0.Senke.Anweisung.Bindung.Pruefung
public import Stage0.Senke.Anweisung.Puffer.Tor
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- The call of a gate without a reason channel: the raw answer is the kernel's word read signed. -/
theorem torC0_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {s : Nat} {c : List II} {top : Nat} {fp pc : Runner.W} {K Ks : Nat}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : torC0 L a args s reserved = some (c, top)) (hKs : top ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K s c ρ reserved) (hWa : WeltAt m L σ) :
    ∃ m' w, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ AgreeW L fp s K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = w.toInt := by
  simp only [torC0] at h
  split at h
  · next h0 =>
    obtain ⟨b, _, m', w, s1, a1, hw, hW', hroh⟩ := torC_ok (O := O) h hKs hW hp hWa
    exact ⟨m', w, s1, a1, hw, hW', by rw [hroh]; simp only [rohW, h0, ↓reduceIte]⟩
  · cases h

theorem torC_top1 {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {s : Nat}
    {reserved : Nat} {c : List II} {t : Nat} (h : torC L a args s reserved = some (c, t)) : s + 7 ≤ t := by
  simp only [torC] at h
  split at h
  · split at h
    · split at h
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl⟩ := h
        omega
      · split at h
        · split at h
          · split at h
            · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, _, _, rfl⟩ := h
              omega
            · cases h
          · cases h
        · cases h
    · cases h
  · cases h

theorem torC_top {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {s : Nat}
    {reserved : Nat} {c : List II} {t : Nat} (h : torC0 L a args s reserved = some (c, t)) : s + 7 ≤ t := by
  simp only [torC0] at h
  split at h
  · exact torC_top1 h
  · cases h

/-! ## G's side: the raw answer decoded -/

theorem axiomAntwort_eq (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O a σ ρ = ((O.wirkt a (σ.fragt (.inl a)) ρ).1,
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ.fragt (.inl a)) ρ).2) := by rfl

/-- A gate without an answer: every raw word decodes. -/
theorem einpassenErg_none {z : Int → Option D.Fn} {e : Option Ty} (he : e = none) (r : Int) :
    ∃ u, einpassenErg z e r = some u := by
  subst he; exact ⟨(), rfl⟩

/-- An integer answer: inside its range the kernel's word is the value's word; outside, no answer. -/
theorem einpassen_int {z : Int → Option D.Fn} {e : Option Ty} {τ : Ty} (he : e = some τ) {lo hi : Int}
    (hτ : τ = .int lo hi) (w : Runner.W) :
    (lo ≤ w.toInt ∧ w.toInt ≤ hi → ∃ v, einpassenErg z e w.toInt = some v ∧ Enc L τ (ergWert he v) w) ∧
    (¬ (lo ≤ w.toInt ∧ w.toInt ≤ hi) → einpassenErg z e w.toInt = none) := by
  subst he hτ
  refine ⟨fun h => ⟨⟨w.toInt, h.1, h.2⟩, ?_, ?_⟩, fun h => ?_⟩
  · simp [einpassenErg, einpassen, h]; try rfl
  · show w = BitVec.ofInt 64 w.toInt
    exact (BitVec.ofInt_toInt).symm
  · simp [einpassenErg, einpassen, h]; try rfl

/-- No raw integer answers a never gate. -/
theorem einpassen_never {z : Int → Option D.Fn} {e : Option Ty}
    (he : e = some .never) (n : Int) : einpassenErg z e n = none := by
  subst he
  rfl

/-- Boolean answers always fit, with zero false and every other raw integer true. -/
theorem einpassen_bool {z : Int → Option D.Fn} {e : Option Ty}
    (he : e = some .bool) (n : Int) :
    ∃ v, einpassenErg z e n = some v ∧ ergWert he v = decide (n ≠ 0) := by
  subst he
  exact ⟨decide (n ≠ 0), rfl, rfl⟩

end Gabbro.Stage0.Senke
