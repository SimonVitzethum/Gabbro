/- Reify readable frame slots as a proof-only integer environment. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Quant.Frame
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

abbrev frameWordTy : Ty := .int (-2^63) (2^63 - 1)
@[simp] theorem frameWordTy_width : valueWords frameWordTy = 1 := by decide

def frameWordCtx (n : Nat) : Ctx := List.replicate n frameWordTy

theorem frameWordEnv {m : Runner.Mem} {fp : Runner.W} {K n : Nat}
    (frame : FrameOK m fp K) (hn : FB + n ≤ K) :
    ∃ ρ : Env D (frameWordCtx n), EnvAt L m fp ρ := by
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
    apply ValueAt.of_enc frameWordTy_width
    · simpa [frei, frameWordCtx] using hw
    · exact (BitVec.ofInt_toInt).symm

/-- The variable representing a concrete frame slot in a reified word context. -/
def frameWordVar : (n i : Nat) → i < n → Var (frameWordCtx n) frameWordTy
  | 0, _, h => False.elim (by omega)
  | n+1, i, h => if e : i = n then by
      subst i
      exact .here
    else .there (frameWordVar n i (by omega))

theorem frameWordVar_slot (n i : Nat) (h : i < n) :
    vslot (frameWordVar n i h) = FB + i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : i = n
    · subst i
      simp [frameWordVar, vslot_here, frei, frameWordCtx]
    · simp only [frameWordVar, e, ↓reduceDIte, ↓reduceIte]
      change vslot (Var.there (frameWordVar n i (by omega)) :
        Var (frameWordTy :: frameWordCtx n) frameWordTy) = FB + i
      rw [vslot_there]
      exact ih (by omega)

/-- A reified slot has a universal load proof, while its value is obtained from
    the concrete environment, never postulated as a floating-point producer. -/
theorem frameWordLoad (n i : Nat) (h : i < n) (ρ : Env D (frameWordCtx n)) :
    WordCode (L := L) ρ (fun _ => True)
      (fun j => some ([ci 2 j (FB+i) 0], j+1))
      (BitVec.ofInt 64 (ρ.get (frameWordVar n i h)).n) := by
  intro fp K j c top hc ht m pc hp
  cases hc
  obtain ⟨w, hr, he⟩ := ValueAt.word frameWordTy (ρ.get (frameWordVar n i h))
    (by trivial) (hp.env _ (frameWordVar n i h))
  rw [frameWordVar_slot] at hr
  change w = BitVec.ofInt 64 (ρ.get (frameWordVar n i h)).n at he
  subst w
  have bound := hp.ctx
  simp [frei, frameWordCtx] at bound
  exact mov_ok hp (by omega) (by omega) hr

end Gabbro.Stage0.Senke
