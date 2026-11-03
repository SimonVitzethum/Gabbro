/- Conditional word composition for the binary64 addition routine. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Gleit.Emission
public import Stage0.Senke.Ausdruck.Wenn
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Select a word with the existing checked branch combinator. The result
    slot is included even when a caller supplies an empty branch generator. -/
def routineChooseL (d : Nat) (condition yes no : Nat → Option (List II × Nat)) :
    Option (List II × Nat) := do
  let code ← wennL d (condition d) (yes d) (no d)
  pure (code.1, max code.2 (d + 1))

/-- The branch's memory postcondition is exactly the word-result contract.
    Branches begin with the original environment and stable outside memory;
    no temporary produced by the condition is assumed by either branch. -/
theorem routineChooseL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {condition yes no : Nat → Option (List II × Nat)} {flag : Bool}
    {yv nv : Runner.W}
    (hc : WordCode (L := L) (reserved := reserved) ρ W condition (Runner.IR.bool flag))
    (hy : flag = true → WordCode (L := L) (reserved := reserved) ρ W yes yv)
    (hn : flag = false → WordCode (L := L) (reserved := reserved) ρ W no nv) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => routineChooseL d condition yes no) (if flag then yv else nv) := by
  intro fp K d code top h hK m pc hp
  simp only [routineChooseL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨body, ceiling⟩, hb, he, ht⟩ := h
  dsimp only at he ht
  subst body
  subst top
  apply wennL_ok hb (by omega) (by omega) (bc := flag)
    (P := fun m' => ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧
      w = if flag then yv else nv)
  · intro c t he ht m pc pre
    exact hc he ht m pc pre
  · intro flagTrue c t he ht m pc pre
    simpa only [Ok, Executes, flagTrue, ite_true] using hy flagTrue he ht m pc pre
  · intro flagFalse c t he ht m pc pre
    simpa only [Ok, Executes, flagFalse, Bool.false_eq_true, ite_false] using
      hn flagFalse he ht m pc pre
  · exact hp

/-- An unsigned comparison is essential for fraction and exponent ordering:
    encoded words may carry the sign bit, and opcode 13 is signed. -/
def routineLessL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) := wordL 27 d (a d) (b (d + 1))

theorem routineLessL_ok {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) (reserved := reserved) (reserved := reserved) ρ W a av)
    (hb : WordCode (L := L) (reserved := reserved) (reserved := reserved) ρ W b bv) :
    WordCode (L := L) (reserved := reserved) (reserved := reserved) ρ W (fun d => routineLessL d a b)
      (Runner.IR.bool (av.ult bv)) :=
  WordCode.bin ha hb (g := fun x y => some (Runner.IR.bool (x.ult y)))
    rfl rfl (by decide : 27 < 256)

/-- Conditional code has the same size as `wennL`; explicitly reserving the
    result slot only raises the temporary ceiling to at least one. -/
theorem routineChooseL_emission
    {condition yes no : Nat → Option (List II × Nat)}
    {nc ny nn wc wy wn : Nat}
    (hc : FloatEmission condition nc wc) (hy : FloatEmission yes ny wy)
    (hn : FloatEmission no nn wn) (bound : 16 * (ny + nn + 2) < 2 ^ 31) :
    FloatEmission (fun d => routineChooseL d condition yes no)
      (nc + ny + nn + 2) (max (max wc (max wy wn)) 1) := by
  intro d
  obtain ⟨code, top, he, hl, ht, ho⟩ := FloatEmission.branch hc hy hn bound d
  refine ⟨code, max top (d + 1), ?_, hl, by omega, ho⟩
  simp only [routineChooseL, he, bind, pure, Option.bind_some]

theorem routineLessL_emission {a b : Nat → Option (List II × Nat)}
    {na nb wa wb : Nat} (ha : FloatEmission a na wa) (hb : FloatEmission b nb wb) :
    FloatEmission (fun d => routineLessL d a b)
      (na + nb + 1) (max (max wa (wb + 1)) 2) :=
  FloatEmission.bin ha hb 27 (by decide)

/-- Both directions emit the checked branch, including its result slot. -/
theorem routineChooseL_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => routineChooseL d
        (fun j => routineLessL j
          (fun k => some ([ci 1 k 2 0], k + 1))
          (fun k => some ([ci 1 k 3 0], k + 1)))
        (fun j => some ([ci 1 j 7 0], j + 1))
        (fun j => some ([ci 1 j 9 0], j + 1))) 7 := by
  have cond := routineLessL_ok (L := L) (reserved := reserved) (ρ := ρ) (W := W)
    (WordCode.const 2 (by decide)) (WordCode.const 3 (by decide))
  have eq : (BitVec.ofInt 64 2).ult (BitVec.ofInt 64 3) = true := by decide
  rw [eq] at cond
  exact routineChooseL_ok cond (fun _ => WordCode.const 7 (by decide))
    (fun _ => WordCode.const 9 (by decide))

#print axioms routineChooseL_ok
#print axioms routineLessL_ok
#print axioms routineChooseL_emission
#print axioms routineChooseL_zeuge
end Gabbro.Stage0.Senke
