module

public import Grammatik.Korpus.Zeugnis.Zeugnis.T2
meta import Grammatik.Korpus.Zeugnis.Zeugnis.T2
public import Grammatik.Korpus.Zeugnis.Zeugnis.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- The float bounds of a type, if it has any: a `some` came from a `.fl`
    type (mirror of `intVonTyp_eq`). -/
theorem flVonTyp_eq {τ : Ty} {lo hi : Int × Int}
    (h : flVonTyp τ = some (lo, hi)) : τ = .fl lo hi := by
  cases τ with
  | int _ _ => simp only [flVonTyp, reduceCtorEq] at h
  | bool => simp only [flVonTyp, reduceCtorEq] at h
  | opt _ => simp only [flVonTyp, reduceCtorEq] at h
  | sum _ => simp only [flVonTyp, reduceCtorEq] at h
  | why _ => simp only [flVonTyp, reduceCtorEq] at h
  | never => simp only [flVonTyp, reduceCtorEq] at h
  | fl lo' hi' =>
    simp only [flVonTyp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | fnptr _ => simp only [flVonTyp, reduceCtorEq] at h
  | ptr _ => simp only [flVonTyp, reduceCtorEq] at h
  | ref _ => simp only [flVonTyp, reduceCtorEq] at h
  | arr _ _ => simp only [flVonTyp, reduceCtorEq] at h
  | str _ => simp only [flVonTyp, reduceCtorEq] at h

/-- What `ctxFlTyp` promises: a `some` names a variable that EXISTS (mirror
    of `ctxTyp_var`). The `Var` witness is rebuilt here, never trusted from
    the print. -/
theorem ctxFlTyp_var (Γ : Ctx) (k : Nat) (lo hi : Int × Int)
    (h : ctxFlTyp Γ k = some (lo, hi)) : ∃ _ : Var Γ (.fl lo hi), True := by
  induction Γ generalizing k with
  | nil =>
    cases k <;> simp only [ctxFlTyp, reduceCtorEq] at h
  | cons τ Γ ih =>
    cases k with
    | zero =>
      cases τ with
      | int _ _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | bool => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | opt _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | sum _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | why _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | never => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | fl lo' hi' =>
        simp only [ctxFlTyp, flVonTyp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.here, trivial⟩
      | fnptr _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | ptr _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | ref _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | arr _ _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
      | str _ => simp only [ctxFlTyp, flVonTyp, reduceCtorEq] at h
    | succ k =>
      simp only [ctxFlTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.there x, trivial⟩


end Gabbro.Grammatik
