module
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Source arithmetic denotation over the entry environment. There is no storage, old-state,
    result or call rule. Name resolution is witnessed at the original parameter position.
    Division and remainder denote the model's truncating operators (`tdiv`/`tmod`): the
    unsigned and the signed lowering evaluate to the same value, only their ranges differ.
    A conversion denotes its operand unchanged: widening preserves the value. -/
inductive SourceValue {u : UProg} {Γ : Ctx} (fn : UFn)
    (constants : List (String × Int)) (env : Env (declOf u) Γ) : SExpr → Int → Prop
  | literal (n : Nat) : SourceValue fn constants env (.lit n) (Int.ofNat n)
  | parameter (name : String) (j : Nat) (lo hi : Int) (v : Var Γ (.int lo hi))
      (found : fn.params[j]? = some (name, .int lo hi))
      (position : lowVar Γ j (.int lo hi) = .ok v) :
      SourceValue fn constants env (.variable name) (env.get v).n
  | constant (name : String) (z : Int)
      (unbound : fn.params.findIdx? (fun p => p.1 == name) = none)
      (found : constants.filter (fun p => p.1 == name) = [(name, z)]) :
      SourceValue fn constants env (.variable name) z
  | add {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "+" a b) (x + y)
  | sub {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "-" a b) (x - y)
  | mul {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "*" a b) (x * y)
  | div {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "/" a b) (x.tdiv y)
  | rem {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "%" a b) (x.tmod y)
  | neg {a : SExpr} {x : Int} (op : String) (spelling : op = "-" ∨ op = "-()") :
      SourceValue fn constants env a x → SourceValue fn constants env (.un op a) (-x)
  | conv {a : SExpr} {x : Int} (name : String) : SourceValue fn constants env a x →
      SourceValue fn constants env (.call name [a]) x
  | band {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y →
      SourceValue fn constants env (.bin "&" a b) ((x.toNat &&& y.toNat : Nat) : Int)
  | bor {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y →
      SourceValue fn constants env (.bin "|" a b) ((x.toNat ||| y.toNat : Nat) : Int)
  | bxor {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y →
      SourceValue fn constants env (.bin "^" a b) ((x.toNat ^^^ y.toNat : Nat) : Int)
  | shl {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y →
      SourceValue fn constants env (.bin "<<" a b) (x * 2 ^ y.toNat)
  | shr {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y →
      SourceValue fn constants env (.bin ">>" a b) (x / 2 ^ y.toNat)

/-- A division that lowers keeps an empty footprint, whatever its range branch. -/
theorem durch_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.durch x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.durch at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h1 : 1 ≤ y.range.1
    · rw [dif_pos h1] at h
      cases h
      change x.term.orte ++ y.term.orte = []
      rw [hx, hy]; rfl
    · rw [dif_neg h1] at h
      by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
      · rw [dif_pos hb] at h
        cases h
        change x.term.orte ++ y.term.orte = []
        rw [hx, hy]; rfl
      · rw [dif_neg hb] at h
        cases h
  · rw [dif_neg h0] at h
    by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
    · rw [dif_pos hb] at h
      cases h
      change x.term.orte ++ y.term.orte = []
      rw [hx, hy]; rfl
    · rw [dif_neg hb] at h
      cases h

/-- A lowered division denotes the truncating source quotient, on both range branches. -/
theorem durch_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.durch x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "/" a b) (eval entry s.term state env).n := by
  unfold LowSide.durch at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h1 : 1 ≤ y.range.1
    · rw [dif_pos h1] at h
      cases h
      exact SourceValue.div dx dy
    · rw [dif_neg h1] at h
      by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
      · rw [dif_pos hb] at h
        cases h
        exact SourceValue.div dx dy
      · rw [dif_neg hb] at h
        cases h
  · rw [dif_neg h0] at h
    by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
    · rw [dif_pos hb] at h
      cases h
      exact SourceValue.div dx dy
    · rw [dif_neg hb] at h
      cases h

/-- A remainder that lowers keeps an empty footprint, whatever its range branch. -/
theorem rest_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.rest x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.rest at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h1 : 1 ≤ y.range.1
    · rw [dif_pos h1] at h
      cases h
      change x.term.orte ++ y.term.orte = []
      rw [hx, hy]; rfl
    · rw [dif_neg h1] at h
      by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
      · rw [dif_pos hb] at h
        cases h
        change x.term.orte ++ y.term.orte = []
        rw [hx, hy]; rfl
      · rw [dif_neg hb] at h
        cases h
  · rw [dif_neg h0] at h
    by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
    · rw [dif_pos hb] at h
      cases h
      change x.term.orte ++ y.term.orte = []
      rw [hx, hy]; rfl
    · rw [dif_neg hb] at h
      cases h

/-- A lowered remainder denotes the truncating source remainder, on both range branches. -/
theorem rest_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.rest x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "%" a b) (eval entry s.term state env).n := by
  unfold LowSide.rest at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h1 : 1 ≤ y.range.1
    · rw [dif_pos h1] at h
      cases h
      exact SourceValue.rem dx dy
    · rw [dif_neg h1] at h
      by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
      · rw [dif_pos hb] at h
        cases h
        exact SourceValue.rem dx dy
      · rw [dif_neg hb] at h
        cases h
  · rw [dif_neg h0] at h
    by_cases hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1
    · rw [dif_pos hb] at h
      cases h
      exact SourceValue.rem dx dy
    · rw [dif_neg hb] at h
      cases h

/-- A conversion that lowers keeps an empty footprint: widening reads nothing new. -/
theorem conv_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x s : LowSide u Γ Λ}
    {lo hi : Int} (hx : x.term.orte = [])
    (h : LowSide.conv lo hi x = .ok s) : s.term.orte = [] := by
  unfold LowSide.conv at h
  by_cases h1 : lo ≤ x.range.1
  · rw [dif_pos h1] at h
    by_cases h2 : x.range.2 ≤ hi
    · rw [dif_pos h2] at h
      cases h
      exact hx
    · rw [dif_neg h2] at h
      cases h
  · rw [dif_neg h1] at h
    cases h

/-- A lowered conversion denotes its operand: widening preserves the value. -/
theorem conv_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x s : LowSide u Γ Λ} {lo hi : Int}
    (h : LowSide.conv lo hi x = .ok s) (a : SExpr) (name : String)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n) :
    SourceValue fn constants env (.call name [a]) (eval entry s.term state env).n := by
  unfold LowSide.conv at h
  by_cases h1 : lo ≤ x.range.1
  · rw [dif_pos h1] at h
    by_cases h2 : x.range.2 ≤ hi
    · rw [dif_pos h2] at h
      cases h
      exact SourceValue.conv name dx
    · rw [dif_neg h2] at h
      cases h
  · rw [dif_neg h1] at h
    cases h

end Gabbro.Grammatik.Parser.Measures
