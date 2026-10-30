/- Reify readable frame slots as a proof-only integer environment. -/
import Stage0.Senke.Ausdruck.Gleit.Skalieren
import Stage0.Senke.Ausdruck.Quant.Frame

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

private abbrev wordTy : Ty := .int (-2^63) (2^63 - 1)
private def wordCtx (n : Nat) : Ctx := List.replicate n wordTy

private theorem frameEnv {m : Runner.Mem} {fp : Runner.W} {K n : Nat}
    (frame : FrameOK m fp K) (hn : FB + n ≤ K) :
    ∃ ρ : Env D (wordCtx n), EnvAt L m fp ρ := by
  induction n with
  | zero => exact ⟨Env.nil, fun _ x => nomatch x⟩
  | succ n ih =>
    obtain ⟨ρ, hρ⟩ := ih (by omega)
    have rd := frame.rd (FB + n) (by omega)
    obtain ⟨w, hw⟩ : ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (FB + n))) = some w := by
      simp only [Runner.Mem.rd64, rd, ↓reduceIte]
      exact ⟨_, rfl⟩
    let v : Zahl (-2^63) (2^63 - 1) :=
      ⟨w.toInt, by simpa using BitVec.le_toInt w,
        by simpa using BitVec.toInt_le (x := w)⟩
    refine ⟨Env.cons v ρ, ?_⟩
    apply envAt_cons hρ
    · simpa [frei, wordCtx] using hw
    · exact (BitVec.ofInt_toInt).symm

/-- A slot load is universally sound only when its input is represented in the
    proof context. This context is built from actual memory reads below. -/
private theorem contextLoad (input : Nat) (hi : FB ≤ input)
    (z : Zahl (-2^63) (2^63 - 1)) (ρ : Env D (wordCtx (input - FB))) :
    WordCode (L := L) (Env.cons (τ := wordTy) z ρ) (fun _ => True)
      (fun j => some ([ci 2 j input 0], j + 1)) (BitVec.ofInt 64 z.n) := by
  intro fp K j c top hc ht m pc hp
  cases hc
  obtain ⟨w, hr, he⟩ := hp.env _ Var.here
  have eqslot : vslot (Var.here : Var (wordTy :: wordCtx (input - FB)) wordTy) = input := by
    simp [vslot_here, frei, wordCtx]; omega
  rw [eqslot] at hr
  change w = BitVec.ofInt 64 z.n at he
  subst w
  have bound := hp.ctx
  simp [frei, wordCtx] at bound
  exact mov_ok hp (by omega) (by omega) hr

/-- Execute the complete explicit-slot continuation from the actual input read.
    The auxiliary environment proves the slot load; it changes no runtime state. -/
theorem floatOfIntContinuationL_ok (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top reserved : Nat}
    {code : List II} (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63)
    (hc : floatOfIntContinuationL F input = some (code, top))
    (hp : Pre L m pc fp K input code ρ W reserved) (ht : top ≤ K)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofInt 64 z)) :
    Ok m pc fp K input code
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  obtain ⟨assembly, ha, he⟩ := floatOfIntContinuationL_parts F input hc
  have ceiling := floatOfIntAssemblyL_ceiling ha
  have hi : FB ≤ input := by have := hp.ctx; unfold frei at this; omega
  obtain ⟨ρbase, env⟩ := frameEnv (L := L) (n := input - FB) hp.frame (by omega)
  let v : Zahl (-2^63) (2^63 - 1) := ⟨z, hz.1, by omega⟩
  have env' : EnvAt L m fp (Env.cons (τ := wordTy) v ρbase) := by
    apply envAt_cons env
    · simpa [frei, wordCtx, show FB + (input - FB) = input by omega] using hr
    · rfl
  rw [he] at hp
  have pre : Pre L m pc fp K (input + 1) assembly (Env.cons (τ := wordTy) v ρbase) (fun _ => True) :=
    ⟨by simp [frei, wordCtx]; omega, hp.small, hp.frame, hp.left.code,
      hp.left.far, env', trivial, wstab_true _ _⟩
  have run : WordCode (L := L) (Env.cons (τ := wordTy) v ρbase) (fun _ => True)
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d
        (fun j => some ([ci 2 j input 0], j + 1)))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) :=
    floatOfIntAssemblyL_ofInt F hF z hz (contextLoad (L := L) input hi v ρbase)
  obtain ⟨m1, s1, a1, _retained, w, r1, hw⟩ :=
    slotRead_after_ok hp.frame (Nat.lt_succ_self input) (by omega) hr
      (run ha ht m pc pre)
  have next := hp.next (a1.mono (Nat.le_succ input)) (Nat.le_refl _) (by omega)
  obtain ⟨m2, s2, a2, r, rr, hrr⟩ := mov_ok (s := input + 1) (d := input) next (by omega) (by omega) r1
  rw [he]
  refine ⟨m2, ?_, (a1.mono (Nat.le_succ input)).trans a2, r, rr, hrr.trans hw⟩
  simpa only [List.length_append, List.length_singleton, pc_add] using s1.trans s2

/-- The actual child run supplies the encoded input to the complete continuation.
    Both ceilings remain part of the emitted candidate's frame bound. -/
theorem computedFloatOfL_ok (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat}
    {child : Nat → Option (List II × Nat)} {code : List II}
    {lo hi : Int} (v : Zahl lo hi) (hlo : -2^63 ≤ lo) (hhi : hi < 2^63)
    (hc : computedFloatOfL F d child = some (code, top))
    (hp : Pre L m pc fp K d code ρ W reserved) (ht : top ≤ K)
    (childRun : ∀ ce, child d = some ce →
      Ok m pc fp K d ce.1 (Enc L (.int lo hi) v)) :
    Ok m pc fp K d code
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F v.n))) := by
  simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hc
  obtain ⟨ce, he, ca, ha, hc⟩ := hc
  cases hc
  obtain ⟨assembly, assemblyOk, _⟩ := floatOfIntContinuationL_parts F d ha
  have ceiling := floatOfIntAssemblyL_ceiling assemblyOk
  apply slotContinuation hp (by omega) (childRun ce he)
  intro m' w pre read hw
  obtain ⟨encoded, lower, upper⟩ := computedFloatOfL_encodedInput v hlo hhi w hw
  subst w
  exact floatOfIntContinuationL_ok F hF v.n ⟨lower, upper⟩ ha pre
    (by omega) read

/-- Candidate for the computed-integer hook. The source interval is checked before
    emitting the child; unsupported intervals remain refusals. Reservation is passed
    to the ordinary expression lowering unchanged. -/
def computedFloatOfE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (F : Gleitkomma.Format) (e : Expr D Γ Λ (.int lo hi))
    (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  if F ∈ [Gleitkomma.f32, Gleitkomma.f64] ∧ -2^63 ≤ lo ∧ hi < 2^63 then
    computedFloatOfL F d (fun j => lowE L e j reserved)
  else none

/-- Top and both child/suffix budgets follow from the actual candidate. -/
theorem computedFloatOfE_bounds {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {F : Gleitkomma.Format} {e : Expr D Γ Λ (.int lo hi)}
    {d reserved top : Nat} {code : List II}
    (hc : computedFloatOfE L F e d reserved = some (code, top)) :
    d < top ∧ ∃ ce ca,
      lowE L e d reserved = some ce ∧
      floatOfIntContinuationL F d = some ca ∧
      code = ce.1 ++ ca.1 ∧ top = max ce.2 ca.2 := by
  unfold computedFloatOfE at hc
  split at hc
  · simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hc
    obtain ⟨ce, he, ca, ha, hc⟩ := hc
    cases hc
    obtain ⟨assembly, assemblyOk, _⟩ := floatOfIntContinuationL_parts F d ha
    have bound := floatOfIntAssemblyL_ceiling assemblyOk
    exact ⟨by omega, ce, ca, he, ha, rfl, rfl⟩
  · cases hc

/-- A hook consumes the ordinary child's simulation at the same reservation.
    No universally movable fixed-slot code is assumed. The returned `Ok` includes
    the footprint agreement below `d` and above the complete frame budget. -/
theorem computedFloatOfE_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {F : Gleitkomma.Format} {e : Expr D Γ Λ (.int lo hi)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {σ₀ σ : World D}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat} {code : List II}
    (hc : computedFloatOfE L F e d reserved = some (code, top))
    (hp : Pre L m pc fp K d code ρ W reserved) (ht : top ≤ K)
    (child : ∀ ce ct, lowE L e d reserved = some (ce, ct) → ct ≤ K →
      Pre L m pc fp K d ce ρ W reserved →
      Ok m pc fp K d ce (Enc L (.int lo hi) (eval σ₀ e σ ρ))) :
    Ok m pc fp K d code
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F
        (Gleitkomma.ofInt F (eval σ₀ e σ ρ).n))) := by
  have shape := computedFloatOfE_bounds hc
  unfold computedFloatOfE at hc
  split at hc
  · next guard =>
    apply computedFloatOfL_ok F guard.1 (eval σ₀ e σ ρ)
      guard.2.1 guard.2.2 hc hp ht
    intro ce he
    obtain ⟨ce', ca, he', _, codeEq, topEq⟩ := shape.2
    have eq : ce = ce' := Option.some.inj (he.symm.trans he')
    subst ce'
    apply child ce.1 ce.2 he (by omega)
    rw [codeEq] at hp
    exact hp.left
  · cases hc

#print axioms computedFloatOfE_ok

#print axioms computedFloatOfL_ok

#print axioms floatOfIntContinuationL_ok
end Gabbro.Stage0.Senke
