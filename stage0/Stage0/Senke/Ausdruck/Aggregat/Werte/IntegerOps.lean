/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/IntegerOps.lean
  Subject:   The integer division, remainder, bitwise and shift cases of `lowE_ok`, one theorem each: the two
             operands' lowerings (as induction hypotheses) give the operation's word. Split out of `Satz.lean`.
-/
module
public import Stage0.Senke.Ausdruck.Tops.Top
public import Stage0.Senke.Ausdruck.Wort.Wort
public import Stage0.Senke.Ausdruck.Aggregat.Werte.IntegerResize
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Shift
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Ring
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Λ : List (Res D)} {Γ : Ctx}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top reserved : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem div_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.div h0 h1' a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.div h0 h1' a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inUE, inU, decide_eq_true_eq] at hw
    refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, udiv_w (by omega) (by omega) (by omega) (by omega), rfl⟩
  · exact wideDiv_ok h0 h1' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem rem_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.rem h0 h1' a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.rem h0 h1' a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inUE, inU, decide_eq_true_eq] at hw
    refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, urem_w (by omega) (by omega) (by omega) (by omega), rfl⟩
  · exact wideRem_ok h0 h1' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem sdiv_ok {l1 h1 l2 h2 : Int} (hb : 1 ≤ l2 ∨ h2 ≤ -1)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.sdiv hb a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.sdiv hb a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
    have := (eval σ₀ a σ ρ).lo_le
    have := (eval σ₀ a σ ρ).le_hi
    refine Ok.value ?_ (integerWords_word (by unfold betragMax; omega) (by unfold betragMax; omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, sdiv_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
  · exact wideSdiv_ok hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem srem_ok {l1 h1 l2 h2 : Int} (hb : 1 ≤ l2 ∨ h2 ≤ -1)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.srem hb a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.srem hb a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inWE, nichtMin, inW, decide_eq_true_eq] at hw
    have := (eval σ₀ b σ ρ).lo_le
    have := (eval σ₀ b σ ρ).le_hi
    refine Ok.value ?_ (integerWords_word (by unfold betragMax; omega) (by unfold betragMax; omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, srem_w (by omega) (by omega) (by omega) (by omega) (by omega), rfl⟩
  · exact wideSrem_ok hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem band_ok {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.band h0 h0' a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.band h0 h0' a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inUE, inU, inWE, inW, decide_eq_true_eq] at hw
    refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, rfl, and_w (by omega) (by omega) (by omega) (by omega)⟩
  · exact wideBand_ok h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem bor_ok {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.bor w h0 h0' hw1 hw2 a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.bor w h0 h0' hw1 hw2 a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
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
    refine binE_ok rawLower rawFits iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, rfl, or_w (by omega) (by omega) (by omega) (by omega)⟩
  · exact wideBor_ok w h0 h0' hw1 hw2 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem bxor_ok {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.bxor w h0 h0' hw1 hw2 a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.bxor w h0 h0' hw1 hw2 a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
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
    refine binE_ok rawLower rawFits iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, rfl, xor_w (by omega) (by omega) (by omega) (by omega)⟩
  · exact wideBxor_ok w h0 h0' hw1 hw2 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem shl_ok {l1 h1 l2 h2 : Int} (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.shl w hw1 hw2 h0 h0' a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.shl w hw1 hw2 h0 h0' a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, inUE, inU, inWE, lt64, inW] at hw
    refine Ok.value ?_ hw.1.1
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, rfl, shl_w _ (by omega) (by omega)⟩
  · exact wideShl_ok w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a)
      (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

theorem shr_ok {l1 h1 l2 h2 : Int} (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (iha : ∀ d' ca ta, lowE L (reserved := reserved) a d' = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d' ca ρ W reserved → ValueOk L m pc fp K d' ca (.int l1 h1) (eval σ₀ a σ ρ))
    (ihb : ∀ d' cb tb, lowE L (reserved := reserved) b d' = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K d' cb ρ W reserved → ValueOk L m pc fp K d' cb (.int l2 h2) (eval σ₀ b σ ρ))
    (h : lowE L (reserved := reserved) (Expr.shr w hw1 hw2 h0 h0' a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c _ (eval σ₀ (Expr.shr w hw1 hw2 h0 h0' a b) σ ρ) := by
  have iha' : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.int l1 h1) (eval σ₀ a σ ρ)) :=
    fun ca ta ha hta m pc hp => (iha d ca ta ha hta m pc hp).word trivial
  have ihb' : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.int l2 h2) (eval σ₀ b σ ρ)) :=
    fun cb tb hb htb m pc hp => (ihb (d + 1) cb tb hb htb m pc hp).word trivial
  simp only [lowE_eqs] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true, inUE, inU, inWE, lt64, inW, decide_eq_true_eq] at hw
    refine Ok.value ?_ (integerWords_unsigned (by decide) (by omega))
    refine binE_ok h hK iha'
      ihb'
      ?_ rfl (by decide) hp
    intro wa wb pa pb
    have a1 := (eval σ₀ a σ ρ).lo_le; have a2 := (eval σ₀ a σ ρ).le_hi
    have b1 := (eval σ₀ b σ ρ).lo_le; have b2 := (eval σ₀ b σ ρ).le_hi
    simp only [Enc] at pa pb
    subst pa pb
    exact ⟨_, rfl, shr_w (by omega) (by omega) (by omega) (by omega)⟩
  · exact wideShr_ok w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ) (fa := lowE L (reserved := reserved) a) (fb := lowE L (reserved := reserved) b) (iha d) (ihb _) h hK hp

end Gabbro.Stage0.Senke
