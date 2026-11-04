module

public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Ausdruck.Gleichungen
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
open Gabbro.Grammatik Runner.Mem
variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A counted expression result carries the same complete typed memory relation
    as ordinary lowering. Scalar specializations are proved through Enc.single. -/
def CountedValueOk (n : Nat) (L : Lay D) (m : Mem) (pc fp : W) (K d : Nat)
    (code : List II) (τ : Ty) (v : Wert D τ) : Prop :=
  ∃ m', Counted n ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
    Agree fp d K m m' ∧ ValueAt L m' fp d τ v

theorem lowE_literal_value_counted {Γ : Ctx} {Λ : List (Res D)} {k : Int}
    (v : Zahl k k) {d top K : Nat} {code : List II} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {W : Mem → Prop}
    (lower : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit k) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedValueOk (literalCount k d) L m pc fp K d code (.int k k) v := by
  have number : v.n = k := by have := v.lo_le; have := v.le_hi; omega
  rw [lowE_lit] at lower
  split at lower
  · next small =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj lower)
    obtain ⟨m', run, changed, w, read, encoded⟩ := const_counted_ok small (by omega) pre
    refine ⟨m', by simpa only [literalCount, small, ite_true] using run,
      changed, ValueAt.of_enc ?_ read ?_⟩
    · have bounds := small
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at bounds
      exact integerWords_word (by omega) (by omega)
    · simpa only [Enc, number] using encoded
  · next large =>
    have pair := Option.some.inj lower
    have codeEq := congrArg Prod.fst pair
    have topEq := congrArg Prod.snd pair
    dsimp only at codeEq topEq
    subst code
    subst top
    have literalEncoding : encodeWords L (.int k k)
        (⟨k, Int.le_refl k, Int.le_refl k⟩ : Zahl k k) =
          integerEncoding (integerWords k k) k :=
      encodeWords_int L k k _
    have canonicalPre : Pre L m pc fp K d
        (constWords (integerEncoding (integerWords k k) k) d).1 ρ W reserved := by
      simpa only [literalEncoding] using pre
    have canonicalFits : (constWords (integerEncoding (integerWords k k) k) d).2 ≤ K := by
      simpa only [literalEncoding] using fits
    obtain ⟨m', run, changed, output⟩ := constWords_counted
      (integerEncoding (integerWords k k) k) canonicalFits canonicalPre
    refine ⟨m', ?_, changed, trivial, ?_⟩
    · simpa only [literalCount, large, Bool.false_eq_true, ↓reduceIte, literalEncoding] using run
    · simpa only [encodeWords_int, number] using output

theorem ExprCost.sound_value {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n : Nat} {v : Wert D τ}
    (certificate : ExprCost L reserved e d n (Enc L τ v))
    {code : List II} {top K : Nat} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {W : Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedValueOk n L m pc fp K d code τ v := by
  rcases certificate.width_or_literal lower with width | ⟨k, sameType, sameExpr, count⟩
  · obtain ⟨m', run, changed, w, read, encoded⟩ := certificate.sound lower fits pre
    exact ⟨m', run, changed, ValueAt.of_enc width read encoded⟩
  · subst τ
    cases sameExpr
    subst n
    exact lowE_literal_value_counted v lower fits pre

/-- Quantitative normal block outcome, retaining the same world, environment
    and protected-slot obligations as `Reach`. -/
def CountedReach (n : Nat) (L : Lay D) {Γ : Ctx} (fp : Runner.W)
    (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem)
    (e : Runner.W) (σ : World D) (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∃ m', Counted n t m ⟨e, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
    EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧ Keeps fp pr m m'

theorem CountedReach.forget {n Γ fp lo K pr t m e σ ρ reserved}
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    Reach L fp lo K pr t m e σ ρ reserved := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- A counted pending hardware request; no hardware completion is asserted. -/
def CountedStops (n : Nat) (t : T) (m : Mem) (c : Nat) : Prop :=
  ∃ t' m' q, Counted n t m t' m' ∧ StopAt t' m' q ∧
    q.nr = 231 ∧ q.a1 = BitVec.ofNat 64 c

theorem CountedStops.forget {n t m c} (h : CountedStops n t m c) : Stops t m c := by
  obtain ⟨t', m', q, run, rest⟩ := h
  exact ⟨t', m', q, run.forget, rest⟩

/-- Return costs use the caller endpoint and the canonical return ABI. -/
def CountedRetZ (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if returnFault P f σ0 σ' ρ0 v ≠ 0
  then CountedStops n t m (returnFault P f σ0 σ' ρ0 v)
  else ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧
      WeltAt m' L (owedWorld P f (σ'.lese (vertragVon D f).ende (P.ensures f).orte))

def CountedRetWhy (n : Nat) (L : Lay D) (f : D.Fn) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (t : T) (m : Runner.Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    ValueAt L m' fp (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
    ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
    ReturnFlag m' fp (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ

def CountedSim (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp : Runner.W)
    {l : Bool} {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem) (e eL eN : Runner.W) (o : Ausgang (vertragVon D f) l Γ) (reserved : Nat := 0) : Prop :=
  match o with
  | .ok σ' ρ' => CountedReach n L fp lo K pr t m e σ' ρ' reserved
  | .leave _ σ' ρ' => CountedReach n L fp lo K pr t m eL σ' ρ' reserved
  | .next _ σ' ρ' => CountedReach n L fp lo K pr t m eN σ' ρ' reserved
  | .zurueck σ' v => CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik c => CountedStops n t m (logikCode c)
  | .hardware h => CountedStops n t m (hwCode h)
  | .why σ' r => CountedRetWhy n L f fp K rp cfp t m σ' r
theorem CountedRetZ.forget {n P f σ0 ρ0 fp K rp cfp t m σ v}
    (h : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t m σ v := by
  unfold CountedRetZ at h
  unfold RetZ
  split at h
  · rename_i hp
    rw [if_pos hp]
    exact h.forget
  · rename_i hp
    rw [if_neg hp]
    obtain ⟨m', run, rest⟩ := h
    exact ⟨m', run.forget, rest⟩

theorem CountedRetWhy.forget {n f fp K rp cfp t m σ r}
    (h : CountedRetWhy n L f fp K rp cfp t m σ r) :
    RetWhy L f fp K rp cfp t m σ r := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- Erasure preserves precisely the existing simulation outcome index. -/
theorem CountedSim.forget {n P f σ0 ρ0 rp cfp l Γ fp lo K pr t m e eL eN reserved}
    {o : Ausgang (vertragVon D f) l Γ}
    (h : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.forget h
  | leave _ σ ρ => exact CountedReach.forget h
  | next _ σ ρ => exact CountedReach.forget h
  | zurueck σ v => exact CountedRetZ.forget h
  | why σ r => exact CountedRetWhy.forget h
  | logik c => exact CountedStops.forget h
  | hardware c => exact CountedStops.forget h

/-- Prefix composition keeps the counted endpoint and all observations joint. -/
theorem CountedReach.prefix {n k Γ fp lo K pr t0 t m0 m e σ ρ reserved}
    (run : Counted k t0 m0 t m) (agree : AgreeW L fp lo K m0 m)
    (keep : Keeps fp pr m0 m)
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    CountedReach (k + n) L fp lo K pr t0 m0 e σ ρ reserved := by
  obtain ⟨m', tail, frame, env, world, kept⟩ := h
  exact ⟨m', run.trans tail, agree.trans frame, env, world, keep.trans kept⟩

theorem CountedStops.prefix {n k t0 t m0 m c}
    (run : Counted k t0 m0 t m) (h : CountedStops n t m c) :
    CountedStops (k + n) t0 m0 c := by
  obtain ⟨t', m', q, tail, rest⟩ := h
  exact ⟨t', m', q, run.trans tail, rest⟩

theorem CountedRetZ.prefix {n k : Nat} {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    CountedRetZ (k + n) L P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [CountedRetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact CountedStops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, hw, hw'⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, hw, hw'⟩

theorem CountedRetWhy.prefix {n k : Nat} {f : D.Fn} {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t0 t : T} {m0 m : Runner.Mem} {σ : World D} {r : Fin (D.gruende f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetWhy n L f fp K rp cfp t m σ r) :
    CountedRetWhy (k + n) L f fp K rp cfp t0 m0 σ r := by
  obtain ⟨m', s, a, hw, flag, hw'⟩ := hs
  exact ⟨m', h.trans s, ha.trans a, hw, flag, hw'⟩

theorem CountedSim.prefix {n k : Nat} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp : W} {l : Bool} {Γ : Ctx}
    {lo K reserved : Nat} {pr : List Nat} {o : Ausgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {e eL eN : Runner.W}
    (hl : FB ≤ lo) (h : Counted k t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m)
    (hs : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) : CountedSim (k + n) L P f σ0 ρ0 rp cfp fp lo K pr t0 m0 e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.prefix h ha hk hs
  | leave _ σ ρ => exact CountedReach.prefix h ha hk hs
  | next _ σ ρ => exact CountedReach.prefix h ha hk hs
  | zurueck σ' v =>
    have hFB3 : FB = 4 := rfl
    exact CountedRetZ.prefix h (ha.mono (by omega)) hs
  | logik c => exact CountedStops.prefix h hs
  | hardware c => exact CountedStops.prefix h hs
  | why σ' r => exact CountedRetWhy.prefix h (ha.mono (by have : FB = 4 := rfl; omega)) hs

/-- Both source loop jumps retain one joint state and execute exactly one
    instruction. The signed displacement is justified by accepted lowering. -/
theorem jmp_counted_reach {Γ : Ctx} {m : Mem} {pc fp : W}
    {lo K reserved : Nat} {pr : List Nat} {x : Int}
    {σ : World D} {ρ : Env D Γ}
    (code : CodeAt m pc [ci 18 (16 + x) 0 0])
    (fits : lit32 (16 + x) = true)
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 1 L fp lo K pr ⟨pc, fp⟩ m
      (pc + 16 + BitVec.ofInt 64 x) σ ρ reserved := by
  have ins := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  have run := Counted.next (run_step (t := ⟨pc, fp⟩) ins (by decide)
    (run_jmp (t := ⟨pc, fp⟩) ins)) (Counted.refl _ _)
  refine ⟨m, ?_, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩
  simpa only [sx_lit fits, BitVec.ofInt_add, BitVec.add_assoc,
    show BitVec.ofInt 64 16 = (16 : W) from rfl] using run

/-- Empty blocks execute no instructions and preserve the entire state. -/
theorem countedBlockNil_case {Γ : Ctx} {fp pc : Runner.W} {lo K : Nat}
    {pr : List Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 0 L fp lo K pr ⟨pc, fp⟩ m pc σ ρ reserved :=
  ⟨m, .refl _ _, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩


end Gabbro.Stage0.Senke
