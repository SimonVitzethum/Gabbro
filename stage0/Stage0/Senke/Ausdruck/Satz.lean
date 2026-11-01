/-
  File:      stage0/Stage0/Senke/Ausdruck/Satz.lean
  Subject:   `lowE_ok`: every expression the lowering accepts computes, in IR, the word of its value in G.
-/
import Stage0.Senke.Ausdruck.Referenz.Lesen
import Stage0.Senke.Ausdruck.Gleit.Fall
import Stage0.Senke.Ausdruck.Lesen
import Stage0.Senke.Ausdruck.Wenn
import Stage0.Senke.Ausdruck.Fnptr
import Stage0.Senke.Ausdruck.Eng
import Stage0.Senke.Ausdruck.Arithmetik.Mixed
import Stage0.Senke.Ausdruck.Tag
import Stage0.Senke.Ausdruck.Aggregat.KopieSatz
import Stage0.Senke.Ausdruck.Aggregat.IntegerResize
import Stage0.Senke.Ausdruck.Aggregat.Array
import Stage0.Senke.Ausdruck.Aggregat.StringOps
import Stage0.Senke.Ausdruck.Option
import Stage0.Senke.Ausdruck.Bytes
import Stage0.Senke.Ausdruck.Quant.Satz
import Stage0.Senke.Ausdruck.Quant.Reach
import Stage0.Senke.Welt.WeltAt
import Stage0.Senke.Welt.Spans.CellStore
import Stage0.Senke.Welt.Spans.Read
import Stage0.Senke.Ausdruck.Referenz.CellIndex
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringEqOk
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringGetOk
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeOk
import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandOk

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

variable {reserved : Nat}

mutual
theorem lowE_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) :
    {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) → (top : Nat) →
    lowE L (reserved := reserved) e d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre L m pc fp K d c ρ W reserved → ValueOk L m pc fp K d c τ (eval σ₀ e σ ρ)
  | _, _, .refEq a b, d, c, top, h, hK, m, pc, ρ, hp =>
    (refEq_ok a b (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
      (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) ca ta ha hta m pc ρ hp).word trivial) h hK hp).value rfl
  | _, _, .slotRef r t ht _ f _, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cr, tr⟩, hr, hs⟩ := h
    have tops := slotValueC_top hs
    have trK : tr ≤ K := by have := tops.1; simp only at this; omega
    have refWord : ∀ m pc, Pre L m pc fp K (d + valueWords (D.typ t f)) cr ρ W reserved →
        Ok m pc fp K (d + valueWords (D.typ t f)) cr (Enc L _ (eval σ₀ r σ ρ)) :=
      fun m pc hp => (lowE_ok σ₀ σ hWL hLay r _ cr tr hr trK m pc ρ hp).word trivial
    obtain ⟨_, _, _, _, _, hv⟩ := refWord m pc (slotValueC_index_pre hs hp)
    obtain ⟨_, _, t', ht', _, hk⟩ := hv
    have same : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst same
    exact slotValueC_ok hs hK hk hLay (fun m pc hp => (refWord m pc hp).mono fun w hw => hw.1) hWL hp
  | _, _, .arrNil, d, c, top, h, hK, m, pc, ρ, hp => arrNil_ok h hK hp
  | _, _, .arrCons a rest, d, c, top, h, hK, m, pc, ρ, hp =>
    arrCons_ok a rest (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay rest _ ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .arrGet a i, d, c, top, h, hK, m, pc, ρ, hp =>
    arrGet_ok a i (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay i _ ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .arrSet a i v, d, c, top, h, hK, m, pc, ρ, hp =>
    arrSet_ok a i v (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay v d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay v _ ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay i _ ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strLit bs hb, d, c, top, h, hK, m, pc, ρ, hp => strLit_ok bs hb h hK hp
  | _, _, .strLen s, d, c, top, h, hK, m, pc, ρ, hp =>
    strLen_ok s (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strCat s t, d, c, top, h, hK, m, pc, ρ, hp =>
    strCat_ok s t (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay t d ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strWeit q s, d, c, top, h, hK, m, pc, ρ, hp =>
    strWeit_ok q s (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strGet s i, d, c, top, h, hK, m, pc, ρ, hp =>
    strGet_ok s i (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay i d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay i _ ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strEq s t, d, c, top, h, hK, m, pc, ρ, hp =>
    strEq_ok s t (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay t (d + 1) ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay t _ ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay t _ ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .strLt s t, d, c, top, h, hK, m, pc, ρ, hp =>
    strCompare_ok true s t (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay s d ca ta ha hta m pc ρ hp)
      (fun ca ta ha hta m pc hp => lowE_ok σ₀ σ hWL hLay t (d + 1) ca ta ha hta m pc ρ hp) h hK hp
  | _, _, .widen lower upper e, d, c, top, h, hK, m, pc, ρ, hp =>
    resizeIntegerL_ok (eval σ₀ e σ ρ) (Zahl.weiter lower upper (eval σ₀ e σ ρ)) rfl
      (fun cc tt hc ht hp => lowE_ok σ₀ σ hWL hLay e d cc tt hc ht m pc ρ hp) h hK hp
  | _, _, .lit n, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next small =>
      have bounds := small
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at bounds
      refine Ok.value ?_ (integerWords_word (by omega) (by omega))
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact (const_ok hp small (by omega)).mono fun _ same => same
    · exact constValue_ok (L := L) (τ := .int n n) ⟨n, by omega, by omega⟩ trivial h hK hp
  | _, _, .fnref f n hf, d, c, top, h, hK, m, pc, ρ, hp => (fnref_ok σ₀ σ h hK hp).value rfl
  | _, _, .tru, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [Enc, eval, wahr?, hw]
  | _, _, .fls, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun w hw => by simp [Enc, eval, wahr?, hw]
  | _, τ, .var x, d, c, top, h, hK, m, pc, ρ, hp => by
    exact var_value_ok x h hK hp
  | _, _, .add a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next width =>
      refine Ok.value ?_ width
      obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
      have := lowE_top b (d + 1) cb tb hb
      refine bin_ok (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
        (fun m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb (by omega) m pc ρ hp).word trivial)
        (g := fun x y => some (x + y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_add]; rfl⟩
    · cases h
  | _, _, .sub a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next width =>
      refine Ok.value ?_ width
      obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
      have := lowE_top b (d + 1) cb tb hb
      refine bin_ok (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
        (fun m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb (by omega) m pc ρ hp).word trivial)
        (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← ofInt_sub']; rfl⟩
    · cases h
  | _, _, .mul a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next width =>
      refine Ok.value ?_ width
      obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
      have := lowE_top b (d + 1) cb tb hb
      refine bin_ok (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
        (fun m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb (by omega) m pc ρ hp).word trivial)
        (g := fun x y => some (x * y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      exact ⟨_, rfl, by simp only [Enc] at pa pb ⊢; rw [pa, pb, ← BitVec.ofInt_mul]; rfl⟩
    · cases h
  | _, _, .fllt a b, d, c, top, h, hK, m, pc, ρ, hp =>
    (floatExprE_ok σ₀ σ false a b
      (fun d c top h hK m pc hp => (lowE_ok σ₀ σ hWL hLay a d c top h hK m pc ρ hp).word trivial)
      (fun d c top h hK m pc hp => (lowE_ok σ₀ σ hWL hLay b d c top h hK m pc ρ hp).word trivial) h hK hp).value rfl
  | _, _, .flle a b, d, c, top, h, hK, m, pc, ρ, hp =>
    (floatExprE_ok σ₀ σ true b a
      (fun d c top h hK m pc hp => (lowE_ok σ₀ σ hWL hLay b d c top h hK m pc ρ hp).word trivial)
      (fun d c top h hK m pc hp => (lowE_ok σ₀ σ hWL hLay a d c top h hK m pc ρ hp).word trivial) h hK hp).value rfl
  | _, _, .and a b, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
      (fun m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb (by omega) m pc ρ hp).word trivial)
      (g := fun x y => some (x &&& y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact and_word _ _
  | _, _, .or a b, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
    have := lowE_top b (d + 1) cb tb hb
    refine bin_ok (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
      (fun m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb (by omega) m pc ρ hp).word trivial)
      (g := fun x y => some (x ||| y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact or_word _ _
  | _, _, .neg a, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next width =>
      refine Ok.value ?_ width
      simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ca, ta⟩, ha, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := lowE_top a (d + 1) ca ta ha
      refine bin_ok (ca := [ci 1 d 0 0]) (fun m pc hp => const_ok hp (by decide) (by omega))
        (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a (d + 1) ca ta ha (by omega) m pc ρ hp).word trivial)
        (g := fun x y => some (x - y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc] at pb ⊢
      rw [pa, pb]
      simp [eval, Zahl.neg, BitVec.ofInt_neg]
    · cases h
  | _, _, .not a, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, ha, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := lowE_top a d ca ta ha
    refine bin_ok (cb := [ci 1 (d + 1) 1 0]) (fun m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp).word trivial)
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact not_word _
  | _, _, @Expr.le _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hc, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine bin_ok (cb := [ci 1 (d + 1) 1 0])
      (Pa := fun w => w = Runner.IR.bool (decide ((eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n)))
      (fun m pc hp => scalarCompareL_ok false
        (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
        (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi
        (fun cb tb hb => lowE_top a (d + 1) cb tb hb)
        (fun ca ta ha fits m pc pre => (lowE_ok σ₀ σ hWL hLay b d ca ta ha fits m pc ρ pre).word trivial)
        (fun cb tb hb fits m pc pre => (lowE_ok σ₀ σ hWL hLay a (d + 1) cb tb hb fits m pc ρ pre).word trivial)
        hc (by omega) hp)
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at ⊢
    rw [pa, pb, bool_word]
    by_cases hl : (eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n
    · have hn : ¬ (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n := by omega
      simp [hl, hn, wahr?]
    · have hn : (eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n := by omega
      simp [hl, hn, wahr?]
  | _, _, @Expr.lt _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    have run := scalarCompareL_ok false
      (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi
      (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
      (fun cb tb hb => lowE_top b (d + 1) cb tb hb)
      (fun ca ta ha fits m pc pre => (lowE_ok σ₀ σ hWL hLay a d ca ta ha fits m pc ρ pre).word trivial)
      (fun cb tb hb fits m pc pre => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb fits m pc ρ pre).word trivial)
      h hK hp
    exact run.mono (fun w value => by
      by_cases comparison : (eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n <;>
        simpa [Enc, eval, bool_word, wahr?, comparison] using value)
  | _, _, @Expr.eq _ _ _ l1 h1 l2 h2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    have run := scalarCompareL_ok true
      (eval σ₀ a σ ρ).lo_le (eval σ₀ a σ ρ).le_hi
      (eval σ₀ b σ ρ).lo_le (eval σ₀ b σ ρ).le_hi
      (fun cb tb hb => lowE_top b (d + 1) cb tb hb)
      (fun ca ta ha fits m pc pre => (lowE_ok σ₀ σ hWL hLay a d ca ta ha fits m pc ρ pre).word trivial)
      (fun cb tb hb fits m pc pre => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb fits m pc ρ pre).word trivial)
      h hK hp
    exact run.mono (fun w value => by
      by_cases comparison : (eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n <;>
        simpa [Enc, eval, bool_word, wahr?, comparison] using value)
  | _, _, .div h0 h1' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, decide_eq_true_eq] at hw
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, udiv_w (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .rem h0 h1' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, decide_eq_true_eq] at hw
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, urem_w (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .sdiv hb a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
      have := (eval σ₀ a σ ρ).lo_le
      have := (eval σ₀ a σ ρ).le_hi
      refine Ok.value ?_ (integerWords_word (by unfold betragMax; omega) (by unfold betragMax; omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, sdiv_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .srem hb a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
      have := (eval σ₀ b σ ρ).lo_le
      have := (eval σ₀ b σ ρ).le_hi
      refine Ok.value ?_ (integerWords_word (by unfold betragMax; omega) (by unfold betragMax; omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, srem_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
    · cases h
  | _, _, .band h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, inWE, inW, decide_eq_true_eq] at hw
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, and_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .bor w h0 h0' hw1 hw2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, inWE, inW, decide_eq_true_eq] at hw
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      let result := eval σ₀ (Expr.bor w h0 h0' hw1 hw2 a b) σ ρ
      have bits := Nat.or_lt_two_pow (x := (eval σ₀ a σ ρ).n.toNat)
        (y := (eval σ₀ b σ ρ).n.toNat) (n := 64) (by omega) (by omega)
      have bitsInt : (((eval σ₀ a σ ρ).n.toNat ||| (eval σ₀ b σ ρ).n.toNat : Nat) : Int) < 2 ^ 64 := by
        exact_mod_cast bits
      let source : Zahl 0 (2 ^ 64 - 1) := ⟨result.n, result.lo_le, by
        change (((eval σ₀ a σ ρ).n.toNat ||| (eval σ₀ b σ ρ).n.toNat : Nat) : Int) ≤ 2 ^ 64 - 1
        omega⟩
      refine resizeIntegerL_ok source result rfl ?_ h hK hp
      intro raw rawTop rawLower rawFits hp
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok rawLower rawFits (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, or_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .bxor w h0 h0' hw1 hw2 a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, inWE, inW, decide_eq_true_eq] at hw
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      let result := eval σ₀ (Expr.bxor w h0 h0' hw1 hw2 a b) σ ρ
      have bits := Nat.xor_lt_two_pow (x := (eval σ₀ a σ ρ).n.toNat)
        (y := (eval σ₀ b σ ρ).n.toNat) (n := 64) (by omega) (by omega)
      have bitsInt : (((eval σ₀ a σ ρ).n.toNat ^^^ (eval σ₀ b σ ρ).n.toNat : Nat) : Int) < 2 ^ 64 := by
        exact_mod_cast bits
      let source : Zahl 0 (2 ^ 64 - 1) := ⟨result.n, result.lo_le, by
        change (((eval σ₀ a σ ρ).n.toNat ^^^ (eval σ₀ b σ ρ).n.toNat : Nat) : Int) ≤ 2 ^ 64 - 1
        omega⟩
      refine resizeIntegerL_ok source result rfl ?_ h hK hp
      intro raw rawTop rawLower rawFits hp
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok rawLower rawFits (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, xor_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .shl _ _ _ h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next width =>
      refine Ok.value ?_ width
      split at h
      · next hw =>
        simp only [Bool.and_eq_true, inUE, inU, inWE, lt64, inW, decide_eq_true_eq] at hw
        refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
          (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
          ?_ rfl (by decide) hp
        intro wa wb pa pb
        have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
        have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
        simp only [Enc] at pa pb
        subst pa pb
        exact ⟨_, rfl, shl_w _ (by omega) (by omega)⟩
      · cases h
    · cases h
  | _, _, .shr _ _ _ h0 h0' a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, inUE, inU, inWE, lt64, inW, decide_eq_true_eq] at hw
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      refine binE_ok h hK (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
        (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial)
        ?_ rfl (by decide) hp
      intro wa wb pa pb
      have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
      have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
      simp only [Enc] at pa pb
      subst pa pb
      exact ⟨_, rfl, shr_w (by omega) (by omega) (by omega) (by omega)⟩
    · cases h
  | _, _, .none n, d, c, top, h, hK, m, pc, ρ, hp =>
    constValue_ok (L := L) (τ := .opt n) none trivial h hK hp
  | _, _, .ptrOf .., d, c, top, h, hK, m, pc, ρ, hp => by
    refine Ok.value ?_ rfl
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (by decide) (by omega)).mono fun _ equal => equal
  | _, _, .why n r, d, c, top, h, hK, m, pc, ρ, hp => by
    exact constValue_ok (L := L) (τ := .why n) r trivial h hK hp
  | _, _, .some e, d, c, top, h, hK, m, pc, ρ, hp =>
    some_ok e (fun d ca ta ha ht m pc hp => lowE_ok σ₀ σ hWL hLay e d ca ta ha ht m pc ρ hp) h hK hp
  | _, _, .istSome e, d, c, top, h, hK, m, pc, ρ, hp =>
    istSome_ok e (fun ce te he hte m pc hp => lowE_ok σ₀ σ hWL hLay e d ce te he hte m pc ρ hp) h hK hp
  | _, _, .glob g _, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    exact globalValueC_ok h hK hWL hp
  | _, _, .slot t f i _, d, c, top, h, hK, m, pc, ρ, hp | _, _, .thru _ t _ f i _, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ci1, ti⟩, hci, hs⟩ := h
    have tops := slotValueC_top hs
    have tiK : ti ≤ K := by have := tops.1; simp only at this; omega
    have hn0 := (eval σ₀ i σ ρ).lo_le
    have hkc : ((eval σ₀ i σ ρ).n.toNat : Int) < D.count t := by have := (eval σ₀ i σ ρ).le_hi; omega
    have toWord : BitVec.ofInt 64 (eval σ₀ i σ ρ).n = BitVec.ofNat 64 (eval σ₀ i σ ρ).n.toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hn0]
    have result := slotValueC_ok (idx := (eval σ₀ i σ ρ).n.toNat) hs hK (L.bounded hkc) hLay
      (fun m pc hp => ((lowE_ok σ₀ σ hWL hLay i _ ci1 ti hci tiK m pc ρ hp).word trivial).mono
        fun w hw => by simp only [Enc] at hw; rw [hw, toWord]) hWL hp
    rw [Int.toNat_of_nonneg hn0] at result
    exact result
  | _, _, .case cs i nutz, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hfit =>
      refine Ok.value ?_ (by simp only [valueWords, hfit, ite_true])
      have hl : cs.length ≤ 256 := by
        simpa only [sumFits, Bool.and_eq_true, decide_eq_true_eq] using
          (show decide (cs.length ≤ 256) = true from (by
            simp only [sumFits, Bool.and_eq_true] at hfit; exact hfit.1))
      exact (lowN_ok σ₀ σ hWL hLay i.val (by have := i.isLt; omega) nutz d c top h hK m pc ρ hp).mono
        (fun w hw => ⟨hfit, hw⟩)
    · cases h
  | _, _, .wenn cond a b, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs, wennL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cc, tc⟩, hc, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, h⟩ := h
    split at h
    · next hlen =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := lowE_top cond d cc tc hc
      refine wenn_ok (bc := wahr? (eval σ₀ cond σ ρ)) hp hlen (by omega)
        (fun hp => (lowE_ok σ₀ σ hWL hLay cond d cc tc hc (by omega) m pc ρ hp).word trivial) ?_ ?_
      · intro hcond m pc hp
        exact Executes.mono (lowE_ok σ₀ σ hWL hLay a d ca ta ha (by omega) m pc ρ hp) fun m' hw => by
          simpa only [eval, hcond, ↓reduceIte] using hw
      · intro hcond m pc hp
        exact Executes.mono (lowE_ok σ₀ σ hWL hLay b d cb tb hb (by omega) m pc ρ hp) fun m' hw => by
          simpa only [eval, hcond, Bool.false_eq_true, ↓reduceIte] using hw
    · cases h
  | _, _, .eng e lo' hi' b, d, c, top, h, hK, m, pc, ρ, hp =>
    (eng_ok h hK
      (fun ce te he hte m pc hp => (lowE_ok σ₀ σ hWL hLay e d ce te he hte m pc ρ hp).word trivial)
      (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b d cb tb hb htb m pc ρ hp).word trivial) hp).value (eng_width h)
  | _, _, .getBytes t f hf n i hlo hhi _, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs] at h
    split at h
    · next hn =>
      have power : (256 : Int) ^ n ≤ (256 : Int) ^ 8 := by
        have natural := Nat.pow_le_pow_right (n := 256) (i := n) (by decide) hn
        have cast : ((256 ^ n : Nat) : Int) ≤ ((256 ^ 8 : Nat) : Int) := Int.ofNat_le.mpr natural
        simpa only [Int.natCast_pow, Int.cast_ofNat_Int] using cast
      have ceiling : (256 : Int) ^ 8 = 2 ^ 64 := by decide
      rw [ceiling] at power
      refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
      have hr := readBytesL_ok i hf hWL hlo
        (fun d ci ti hi ht m pc hp => (lowE_ok σ₀ σ hWL hLay i d ci ti hi ht m pc ρ hp).word trivial)
        n 0 d c top (by simpa using hhi) (by omega) h hK m pc hp
      exact hr.mono (fun w hw => by
        change w = BitVec.ofInt 64 (bytesZuZahl (σ.bytesAb t f hf n (eval σ₀ i σ ρ).n))
        simpa only [Int.natCast_zero, Int.add_zero] using hw)
    · cases h
  | _, _, .forallSlots t body _, d, c, top, h, hK, m, pc, ρ, hp =>
    (quantL_ok true (D.count t) (lowE L (reserved := reserved) body (d + 3)) (fun k => wahr? (eval σ₀ body σ (.cons k ρ))) h hK
      (fun cb tb hb htb k m pc hp => (lowE_ok σ₀ σ hWL hLay body (d + 3) cb tb hb htb m pc (.cons k ρ) hp).word trivial) hp).value rfl
  | _, _, .existsSlots t body _, d, c, top, h, hK, m, pc, ρ, hp =>
    (quantL_ok false (D.count t) (lowE L (reserved := reserved) body (d + 3)) (fun k => wahr? (eval σ₀ body σ (.cons k ρ))) h hK
      (fun cb tb hb htb k m pc hp => (lowE_ok σ₀ σ hWL hLay body (d + 3) cb tb hb htb m pc (.cons k ρ) hp).word trivial) hp).value rfl
  | _, _, .reaches t f hf a b _, d, c, top, h, hK, m, pc, ρ, hp =>
    (reachesL_ok hf hWL (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) h hK
      (fun ca ta ha hta m pc hp => (lowE_ok σ₀ σ hWL hLay a d ca ta ha hta m pc ρ hp).word trivial)
      (fun cb tb hb htb m pc hp => (lowE_ok σ₀ σ hWL hLay b (d + 1) cb tb hb htb m pc ρ hp).word trivial) hp).value rfl
  | _, _, .oldG .., _, _, _, h, _, _, _, _, _
  | _, _, .oldS .., _, _, _, h, _, _, _, _, _
    => by simp [lowE_eqs] at h
theorem lowN_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop}
    (σ₀ σ : World D) (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) (tag : Nat) (htag : tag < 256) :
    {Γ : Ctx} → {a : Option (Int × Int)} → (nutz : NutzlastExpr D Γ Λ a) → (d : Nat) →
    (c : List II) → (top : Nat) → lowN L (reserved := reserved) tag nutz d = some (c, top) → top ≤ K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ), Pre L m pc fp K d c ρ W reserved →
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64 (tag + 256 * sumOff a (evalNutz σ₀ nutz σ ρ)))
  | _, _, .empty, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp (lit32_nat (by omega)) (by omega)).mono (fun w hw => by
      simpa only [evalNutz, sumOff, Nat.mul_zero, Nat.add_zero, BitVec.ofInt_natCast] using hw)
  | _, _, .num e, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    exact packSum_ok (by simp only [packSum, bin2] at hK; omega) htag
      (by simp only [packSum, bin2] at hK; omega)
      (fun m pc hp => (lowE_ok σ₀ σ hWL hLay e d ce te he
        (by simp only [packSum, bin2] at hK; omega) m pc ρ hp).word trivial) hp
end
end Gabbro.Stage0.Senke
